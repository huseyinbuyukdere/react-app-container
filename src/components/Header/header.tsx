import React from 'react'
import styles from  './header.module.css';
import { MenuItem } from '../../models'
import HeaderMenu from '../HeaderMenu'

interface HeaderProps {
    leftContent?: any
    rightContent?: any
    pageName?: any
    menu?: MenuItem[]
}

export default function Header(props: HeaderProps) {
    var rightContent = props.rightContent ? (
        props.rightContent
    ) : (
        <HeaderMenu itemList={props.menu ? props.menu : []} />
    )
    return (
        <div className={styles.headerContainer}>
            {props.pageName && (
                <div className={styles.pageNameContent}>{props.pageName}</div>
            )}
            <div className={styles.headerLeftContent}>{props.leftContent}</div>
            <div className={styles.headerRightContent}>
                {rightContent}
            </div>
        </div>
    )
}
