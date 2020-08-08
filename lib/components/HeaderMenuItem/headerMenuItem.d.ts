import React from 'react';
interface MenuItemProps {
    label?: string;
    onClick: (routeKey?: string) => void;
    iconComp?: any;
    iconName?: string;
    iconCompStyle?: React.CSSProperties;
    style?: React.CSSProperties;
}
export default function MenuItem(props: MenuItemProps): JSX.Element;
export {};
