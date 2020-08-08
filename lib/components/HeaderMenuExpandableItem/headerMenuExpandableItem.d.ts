import React from 'react';
import { MenuItem as MenuItemContract } from '../../models';
interface HeaderMenuExpandableItemProps {
    label?: string;
    onClick?: (routeKey?: string) => void;
    iconComp?: any;
    iconName?: string;
    iconCompStyle?: React.CSSProperties;
    subMenuItemList: MenuItemContract[];
    style?: React.CSSProperties;
}
declare const HeaderMenuExpandableItem: (props: HeaderMenuExpandableItemProps) => JSX.Element;
export default HeaderMenuExpandableItem;
